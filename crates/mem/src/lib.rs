//! Allocation metering. Register `CountingAlloc` as `#[global_allocator]` and
//! the whole process's heap becomes measurable - the "total load" number is
//! reported, not estimated. Contains the project's single `unsafe` site:
//! the allocator shim itself.

use std::alloc::{GlobalAlloc, Layout, System};
use std::sync::atomic::{AtomicUsize, Ordering};

pub struct CountingAlloc;

static LIVE: AtomicUsize = AtomicUsize::new(0);
static PEAK: AtomicUsize = AtomicUsize::new(0);

fn bump_peak(live: usize) {
    let mut prev = PEAK.load(Ordering::Relaxed);
    while live > prev {
        match PEAK.compare_exchange_weak(prev, live, Ordering::Relaxed, Ordering::Relaxed) {
            Ok(_) => return,
            Err(p) => prev = p,
        }
    }
}

unsafe impl GlobalAlloc for CountingAlloc {
    unsafe fn alloc(&self, l: Layout) -> *mut u8 {
        let p = unsafe { System.alloc(l) };
        if !p.is_null() {
            bump_peak(LIVE.fetch_add(l.size(), Ordering::Relaxed) + l.size());
        }
        p
    }

    unsafe fn dealloc(&self, p: *mut u8, l: Layout) {
        unsafe { System.dealloc(p, l) };
        LIVE.fetch_sub(l.size(), Ordering::Relaxed);
    }
}

/// Bytes currently allocated on the heap.
pub fn live_bytes() -> usize {
    LIVE.load(Ordering::Relaxed)
}

/// Maximum live bytes observed so far.
pub fn peak_bytes() -> usize {
    PEAK.load(Ordering::Relaxed)
}

/// Peak resident set of this process, bytes (Linux /proc, None elsewhere).
pub fn rss_peak_bytes() -> Option<usize> {
    let status = std::fs::read_to_string("/proc/self/status").ok()?;
    for line in status.lines() {
        if let Some(rest) = line.strip_prefix("VmHWM:") {
            let kb: usize = rest.trim().trim_end_matches(" kB").trim().parse().ok()?;
            return Some(kb * 1024);
        }
    }
    None
}
