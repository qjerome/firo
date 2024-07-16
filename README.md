
<!-- cargo-rdme start -->

# Firo

`firo` is a straightforward crate, inspired by `std::fs::File`,
providing the necessary APIs to implement rotating files.

It currently supports:
- rotation trigger based on time
- rotation trigger based on size
- file compression (at rotation time)
- maximum size limit, oldest files will start being deleted if
the sum of all files sizes goes beyond the limit
- **transparently reading** a rotating file

# Usage Example

## Basic

```rust
use firo::{File, OpenOptions, Trigger, Compression};
use std::io::Write;
use std::time::Duration;

let td = tempfile::tempdir().unwrap();

// we initialize a rotating file options
let mut f = File::options()
    // file will rotate every hours
    .trigger(Duration::from_secs(3600).into())
    // finally create the file
    .create_append(td.path().join("test.log")).unwrap();

// one can use File as std::fs::File
for _ in 0..1000 {
    writeln!(f, "rotating every hour").unwrap();
}

```

## Advanced

Rotating file based on size, enabling compression and
deleting old files when total size reaches a given
threshold.

```rust
use firo::{File, OpenOptions, Trigger, Compression};
use huby::ByteSize;
use tempfile;
use std::io::{BufReader, BufRead, Write};

let td = tempfile::tempdir().unwrap();
let p = td.path().join("test.log");
// we initialize a rotating file options
let opts = File::options()
    // file will rotate when reaching 1 KB
    .trigger(ByteSize::from_kb(1).into())
    // gzip compression is enabled (at rotation time)
    .compression(Compression::Gzip)
    // we start deleting oldest file when total size > 1 GB
    .max_size(ByteSize::from_gb(1));

let mut f = opts
    // finally create the file
    .create_append(&p).unwrap();

// one can use File as std::fs::File
for i in 0..100_000 {
    writeln!(f, "{i}").unwrap();
}

// make sure there are no pending writes
f.sync().unwrap();

// one can also read a rotating file
let f = opts.open(p).unwrap();
// we check that file is actually made of several
// files on disk (just for the demo)
assert!(f.files_sorted_by_index().unwrap().len() > 1);
let reader = BufReader::new(f);
let mut lines = reader.lines();

for i in 0..100_000 {
    let line = lines.next().unwrap().unwrap();
    let cmp = line.parse::<u32>().unwrap();
    assert_eq!(i, cmp);
}
```

<!-- cargo-rdme end -->
