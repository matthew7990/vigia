# vigia - agent-native browser, built from scratch
# Usage: make build | test | check | bench | release

build:
	cargo build -p vigia

release:
	cargo build --release -p vigia

test:
	cargo test --workspace

check:
	cargo fmt --check
	cargo clippy --workspace -- -D warnings

# Benchmark against lightpanda (expects the binary at bench/bin/lightpanda,
# regenerates the local corpus, writes bench/out/). Serves the corpus on
# 127.0.0.1:8899 as bench/run.py expects.
bench: release
	python3 bench/gen_corpus.py
	(cd bench/corpus && exec python3 -m http.server 8899) & \
		SRV=$$!; sleep 0.5; python3 bench/run.py; kill $$SRV 2>/dev/null || true

demo:
	cargo build -p vigia && ./target/debug/vigia snap https://example.com

.PHONY: build release test check bench demo
