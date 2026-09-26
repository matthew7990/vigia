#!/usr/bin/env python3
"""vigia vs lightpanda benchmark.

Per page x tool: wall time, child peak RSS (wait4/ru_maxrss), output bytes
and ~tokens (chars/4). Median of N runs.

Usage: python3 bench/run.py [--runs N] [--pages name,...] [--host 127.0.0.1:8899]
Expects a static server on --host serving bench/corpus/ (python3 -m http.server).
"""
import argparse, json, os, sys, time

ROOT = os.path.dirname(os.path.abspath(__file__))
VIGIA = os.path.join(ROOT, "../target/release/vigia")
LP = os.path.join(ROOT, "bin/lightpanda")

TOOLS = {
    # agent-facing output: the page representation an LLM consumes
    "vigia": [VIGIA, "snap"],
    "lightpanda": [LP, "fetch", "--dump", "semantic_tree_text"],
}


def measure(cmd, outfile):
    """Run cmd, capture stdout to outfile. Returns (wall_ms, rss_kb, rc)."""
    pid = os.fork()
    if pid == 0:
        fd = os.open(outfile, os.O_WRONLY | os.O_CREAT | os.O_TRUNC)
        os.dup2(fd, 1)
        devnull = os.open(os.devnull, os.O_WRONLY)
        os.dup2(devnull, 2)
        try:
            os.execvp(cmd[0], cmd)
        except OSError:
            os._exit(127)
    t0 = time.monotonic()
    _, status, ru = os.wait4(pid, 0)
    ms = (time.monotonic() - t0) * 1000
    rc = os.waitstatus_to_exitcode(status)
    return ms, ru.ru_maxrss, rc


def median(xs):
    xs = sorted(xs)
    return xs[len(xs) // 2]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--runs", type=int, default=3)
    ap.add_argument("--host", default="127.0.0.1:8899")
    ap.add_argument("--pages", default="")
    args = ap.parse_args()

    corpus = os.path.join(ROOT, "corpus")
    pages = sorted(f for f in os.listdir(corpus) if f.endswith(".html"))
    if args.pages:
        want = set(args.pages.split(","))
        pages = [p for p in pages if p in want or p[:-5] in want]

    out_dir = os.path.join(ROOT, "out")
    os.makedirs(out_dir, exist_ok=True)

    rows = []
    for page in pages:
        url = f"http://{args.host}/{page}"
        for tool, base in TOOLS.items():
            outfile = os.path.join(out_dir, f"{tool}-{page}.txt")
            times, rss = [], []
            rc = -1
            for _ in range(args.runs):
                ms, kb, rc = measure(base + [url], outfile)
                times.append(ms)
                rss.append(kb)
            size = os.path.getsize(outfile) if rc == 0 else 0
            rows.append({
                "page": page, "tool": tool, "ms": round(median(times), 1),
                "rss_mb": round(median(rss) / 1024, 1), "out_bytes": size,
                "est_tokens": size // 4, "rc": rc,
            })

    print(f"{'page':<16} {'tool':<11} {'ms':>8} {'rss_mb':>8} {'out_b':>8} {'~tokens':>8} rc")
    for r in rows:
        print(f"{r['page']:<16} {r['tool']:<11} {r['ms']:>8} {r['rss_mb']:>8} "
              f"{r['out_bytes']:>8} {r['est_tokens']:>8} {r['rc']}")

    with open(os.path.join(out_dir, "results.json"), "w") as f:
        json.dump(rows, f, indent=2)


if __name__ == "__main__":
    main()
