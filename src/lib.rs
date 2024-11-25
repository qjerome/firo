//! # Firo
//!
//! `firo` is a straightforward crate, inspired by `std::fs::File`,
//! providing the necessary APIs to implement rotating files.
//!
//! It currently supports:
//! - rotation trigger based on time
//! - rotation trigger based on size
//! - file compression (at rotation time)
//! - maximum size limit, oldest files will start being deleted if
//! the sum of all files sizes goes beyond the limit
//! - **transparently reading** a rotating file
//!
//! # Usage Example
//!
//! ## Basic
//!
//! ```
//! use firo::{File, OpenOptions, Trigger, Compression};
//! use std::io::Write;
//! use std::time::Duration;
//!
//! let td = tempfile::tempdir().unwrap();
//!
//! // we initialize a rotating file options
//! let mut f = File::options()
//!     // file will rotate every hours
//!     .trigger(Duration::from_secs(3600).into())
//!     // finally create the file
//!     .create_append(td.path().join("test.log")).unwrap();
//!
//! // one can use File as std::fs::File
//! for _ in 0..1000 {
//!     writeln!(f, "rotating every hour").unwrap();
//! }
//!
//! ```
//!
//! ## Advanced
//!
//! Rotating file based on size, enabling compression and
//! deleting old files when total size reaches a given
//! threshold.
//!
//! ```
//! use firo::{File, OpenOptions, Trigger, Compression};
//! use huby::ByteSize;
//! use tempfile;
//! use std::io::{BufReader, BufRead, Write};
//!
//! let td = tempfile::tempdir().unwrap();
//! let p = td.path().join("test.log");
//! // we initialize a rotating file options
//! let mut opts = File::options();
//! opts
//!     // file will rotate when reaching 1 KB
//!     .trigger(ByteSize::from_kb(1).into())
//!     // gzip compression is enabled (at rotation time)
//!     .compression(Compression::Gzip)
//!     // we start deleting oldest file when total size > 1 GB
//!     .max_size(ByteSize::from_gb(1));
//!
//! let mut f = opts
//!     // finally create the file
//!     .create_append(&p).unwrap();
//!
//! // one can use File as std::fs::File
//! for i in 0..100_000 {
//!     writeln!(f, "{i}").unwrap();
//! }
//!
//! // make sure there are no pending writes
//! f.sync().unwrap();
//!
//! // one can also read a rotating file
//! let f = opts.open(p).unwrap();
//! // we check that file is actually made of several
//! // files on disk (just for the demo)
//! assert!(f.files_sorted_by_index().unwrap().len() > 1);
//! let reader = BufReader::new(f);
//! let mut lines = reader.lines();
//!
//! for i in 0..100_000 {
//!     let line = lines.next().unwrap().unwrap();
//!     let cmp = line.parse::<u32>().unwrap();
//!     assert_eq!(i, cmp);
//! }
//! ```

use std::{
    fs::{self, Metadata},
    io::{self, BufRead, BufReader, BufWriter, Write},
    path::{Path, PathBuf},
    thread,
    time::{Duration, SystemTime},
};

use flate2::{read::GzDecoder, write::GzEncoder};
use huby::ByteSize;
#[cfg(windows)]
use std::os::windows::fs::MetadataExt;
#[cfg(target_family = "unix")]
use std::{
    fs::Permissions,
    os::unix::fs::{MetadataExt, OpenOptionsExt, PermissionsExt},
};
use tempfile::{NamedTempFile, PersistError};
use thiserror::Error;

#[cfg(target_family = "unix")]
mod unix;

/// helper function to add an extension to a Path
#[inline(always)]
fn add_extension<P: AsRef<Path>, S: AsRef<str>>(path: P, ext: S) -> PathBuf {
    let tmp = path.as_ref().to_string_lossy();
    let san_path = tmp.trim_end_matches('.');
    let ext = ext.as_ref().trim_start_matches('.');
    format!("{san_path}.{ext}").into()
}

#[inline(always)]
fn match_ext<P: AsRef<Path>, S: AsRef<str>>(p: P, ext: S) -> bool {
    if let Some(e) = p.as_ref().extension() {
        return ext.as_ref() == e;
    }
    false
}

#[inline(always)]
fn file_size(meta: &Metadata) -> u64 {
    #[cfg(unix)]
    return meta.size();

    #[cfg(windows)]
    return meta.file_size();
}

/// Trigger enumeration used to configure when [File] rotation
/// happens.
#[derive(Debug, Clone, Copy)]
pub enum Trigger {
    /// Size based trigger: will rotate file when current file
    /// reaches a given size.
    Size(ByteSize),
    /// Duration based trigger: will rotate file when duration since
    /// file creation reaches a given duration.
    Time(Duration),
}

impl From<Duration> for Trigger {
    fn from(value: Duration) -> Self {
        Self::Time(value)
    }
}

impl From<ByteSize> for Trigger {
    fn from(value: ByteSize) -> Self {
        Self::Size(value)
    }
}

/// Enumeration to configure compression type
#[derive(Debug, Clone, Copy)]
pub enum Compression {
    Gzip,
}

#[derive(Debug, Error)]
pub enum CompressionError {
    #[error("persist: {0}")]
    Persist(#[from] PersistError),
    #[error("io: {0}")]
    Io(#[from] io::Error),
}

impl Compression {
    const fn extension(&self) -> &'static str {
        match self {
            Compression::Gzip => "gz",
        }
    }

    /// Compression agnostic routine
    fn compress<P: AsRef<Path>>(&self, path: P, mode: Option<u32>) -> Result<(), CompressionError> {
        match self {
            Self::Gzip => Self::compress_gzip(path, mode),
        }
    }

    #[allow(unused_variables)]
    fn compress_gzip<P: AsRef<Path>>(path: P, mode: Option<u32>) -> Result<(), CompressionError> {
        let path = path.as_ref();
        let tmp = NamedTempFile::new()?;
        let mut reader = BufReader::new(fs::File::open(path)?);
        let writer = BufWriter::new(&tmp);
        let mut enc = GzEncoder::new(writer, flate2::Compression::best());

        // Read chunks until the end of the file
        loop {
            let buf = reader.fill_buf()?;

            // we reached EOF
            if buf.is_empty() {
                break;
            }

            enc.write_all(buf)?;

            let length = buf.len();
            reader.consume(length);
        }

        // we make sure everything is flushed to the temp file
        enc.finish()?;

        let new = add_extension(path, Compression::Gzip.extension());

        tmp.persist(&new)?;

        #[cfg(unix)]
        if let Some(mode) = mode {
            fs::set_permissions(new, Permissions::from_mode(mode))?;
        }

        fs::remove_file(path)?;

        Ok(())
    }
}

/// Structure to use to configure [File] options
///
/// # Example
///
/// ```
/// use firo::{File, OpenOptions, Trigger, Compression};
/// use huby::ByteSize;
/// use tempfile;
/// use std::io::Write;
///
/// let td = tempfile::tempdir().unwrap();
///
/// let mut f = File::options()
///     // file will rotate when reaching 10 MB
///     .trigger(Trigger::Size(ByteSize::from_mb(10)))
///     // Gzip compression is enabled
///     .compression(Compression::Gzip)
///     // We start overwriting file when total size > 1 GB
///     .max_size(ByteSize::from_gb(1))
///     .create_append(td.path().join("test.log")).unwrap();
///
/// // one can use File as std::fs::File
/// for _ in 0..1000 {
///     writeln!(f, "some stuff").unwrap();
/// }
/// ```

#[derive(Default, Debug, Clone, Copy)]
pub struct OpenOptions {
    max_size: Option<ByteSize>,
    trigger: Option<Trigger>,
    compression: Option<Compression>,
    #[cfg(target_family = "unix")]
    ext: UnixExt,
}

#[cfg(target_family = "unix")]
#[derive(Default, Debug, Clone, Copy)]
struct UnixExt {
    mode: Option<u32>,
    flags: Option<i32>,
}

impl OpenOptions {
    pub fn new() -> Self {
        Self::default()
    }

    /// Configure the maximum size allowed for a rotating [File].
    /// When the size goes beyond the threshold, oldest files get
    /// deleted
    pub fn max_size(&mut self, m: ByteSize) -> &mut Self {
        self.max_size = Some(m);
        self
    }

    /// Configure the [Trigger] used to rotate file
    pub fn trigger(&mut self, t: Trigger) -> &mut Self {
        self.trigger = Some(t);
        self
    }

    /// Configure desired [Compression]
    pub fn compression(&mut self, c: Compression) -> &mut Self {
        self.compression = Some(c);
        self
    }

    /// Create a [File] in append mode from options
    pub fn create_append<P: AsRef<Path>>(self, path: P) -> Result<File, Error> {
        File::create_append_with_options(path, self)
    }

    /// Open a [File] for reading
    pub fn open<P: AsRef<Path>>(self, path: P) -> Result<File, Error> {
        File::open_with_options(path, self)
    }
}

#[derive(Debug)]
enum R {
    File(BufReader<fs::File>),
    Gzip(GzDecoder<BufReader<fs::File>>),
}

impl R {
    fn open<P: AsRef<Path>>(p: P) -> Result<Self, Error> {
        let br = BufReader::new(fs::File::open(p.as_ref())?);
        if match_ext(p, Compression::Gzip.extension()) {
            Ok(Self::Gzip(GzDecoder::new(br)))
        } else {
            Ok(Self::File(br))
        }
    }
}

impl io::Read for R {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        match self {
            Self::File(f) => f.read(buf),
            Self::Gzip(d) => d.read(buf),
        }
    }
}

#[derive(Debug)]
struct Reader {
    files: Vec<PathBuf>,
    reader: R,
}

impl io::Read for Reader {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        let read = self.reader.read(buf)?;

        // if we reached EOF and we still have files
        if read == 0 && !self.files.is_empty() {
            let f = self.files.pop().unwrap();
            self.reader = R::open(f)?;
            return self.reader.read(buf);
        }

        Ok(read)
    }
}

impl Reader {
    fn from_file(f: &File) -> Result<Self, Error> {
        let mut files = f.files_sorted_by_index()?;
        files.reverse();
        if files.is_empty() {
            return Err(Error::NoSuchFile(f.file_path()));
        }

        let f = files.pop().unwrap();
        let reader = R::open(f)?;

        Ok(Self { files, reader })
    }
}

#[derive(Debug, Default)]
pub struct File {
    #[cfg(target_family = "unix")]
    ext: UnixExt,
    dir: PathBuf,
    prefix: String,
    size: u64,
    created: Option<SystemTime>,
    writer: Option<BufWriter<fs::File>>,
    reader: Option<Reader>,
    max_size: Option<ByteSize>,
    trigger: Option<Trigger>,
    compression: Option<Compression>,
    compress_job: Option<thread::JoinHandle<Result<(), CompressionError>>>,
}

#[derive(Error, Debug)]
pub enum Error {
    #[error("not open for read")]
    WrongModeRead,
    #[error("not open for write")]
    WrongModeWrite,
    #[error("no such file: {0}")]
    NoSuchFile(PathBuf),
    #[error("file is closed")]
    FileClosed,
    #[error("file prefix not found: {0}")]
    PrefixNotFound(PathBuf),
    #[error("root directory not found: {0}")]
    RootNotFound(PathBuf),
    #[error("io: {0}")]
    Io(#[from] io::Error),
    #[error("compression: {0}")]
    Compression(#[from] CompressionError),
}

// Converts Error into io::Error
impl From<Error> for io::Error {
    fn from(value: Error) -> Self {
        match value {
            Error::Io(io) => io,
            _ => io::Error::other(value),
        }
    }
}

impl io::Write for File {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        if self.should_rotate() {
            self.rotate()?;
        }

        if let Some(writer) = self.writer.as_mut() {
            let len = writer.write(buf)?;
            self.size = self.size.wrapping_add(len as u64);
            Ok(len)
        } else {
            Err(io::Error::other(Error::WrongModeWrite))
        }
    }

    fn flush(&mut self) -> io::Result<()> {
        if let Some(f) = self.writer.as_mut() {
            f.flush()?;
        }
        Ok(())
    }
}

impl io::Read for File {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        if let Some(r) = self.reader.as_mut() {
            r.read(buf)
        } else {
            Err(io::Error::other(Error::WrongModeRead))
        }
    }
}

impl File {
    fn new<P: AsRef<Path>>(file: P, opts: OpenOptions) -> Result<Self, Error> {
        let file = file.as_ref();

        let prefix = file
            .file_name()
            .ok_or(Error::PrefixNotFound(file.to_path_buf()))?;

        let dir = file
            .parent()
            .ok_or(Error::RootNotFound(file.to_path_buf()))?
            .canonicalize()?
            .to_path_buf();

        Ok(Self {
            #[cfg(target_family = "unix")]
            ext: opts.ext,
            dir,
            prefix: prefix.to_string_lossy().into(),
            size: 0,
            created: None,
            writer: None,
            reader: None,
            max_size: opts.max_size,
            trigger: opts.trigger,
            compression: opts.compression,
            compress_job: None,
        })
    }

    /// Constructs default [OpenOptions] to use for building
    /// a rotating [File]
    pub fn options() -> OpenOptions {
        OpenOptions::default()
    }

    /// Returns the [OpenOptions] used by the current [File].
    pub fn open_options(&self) -> OpenOptions {
        OpenOptions {
            max_size: self.max_size,
            trigger: self.trigger,
            compression: self.compression,
            #[cfg(target_family = "unix")]
            ext: self.ext,
        }
    }

    /// Creates a new rotating [File]
    pub fn create_append<P: AsRef<Path>>(file: P) -> Result<Self, Error> {
        Self::create_append_with_options(file, OpenOptions::default())
    }

    /// Opening an existing rotating [File] with [OpenOptions]
    pub fn open_with_options<P: AsRef<Path>>(file: P, opts: OpenOptions) -> Result<Self, Error> {
        let mut f = Self::new(file, opts)?;

        f.reader = Some(Reader::from_file(&f)?);

        Ok(f)
    }

    /// Creates a new rotating [File] with the given [OpenOptions]
    pub fn create_append_with_options<P: AsRef<Path>>(
        file: P,
        opts: OpenOptions,
    ) -> Result<Self, Error> {
        let mut f = Self::new(file, opts)?;

        f.init_create_append()?;

        Ok(f)
    }

    /// Return the path to the [File]. This [Path] is always
    /// the one of the current file being written.
    #[inline(always)]
    pub fn file_path(&self) -> PathBuf {
        self.dir.join(&self.prefix)
    }

    #[inline(always)]
    fn file_index<P: AsRef<Path>>(&self, p: P) -> Option<u64> {
        let p = p.as_ref();
        if let Some(file_name) = p.file_name().map(PathBuf::from) {
            if !file_name.to_string_lossy().starts_with(&self.prefix) {
                return None;
            }

            // if filename is current file index is 0
            if file_name == PathBuf::from(&self.prefix) {
                return Some(0);
            }

            /// idx from file name
            macro_rules! idx {
                ($p:expr) => {{
                    if let Some(ext) = $p.extension().map(|e| e.to_string_lossy()) {
                        if let Ok(i) = ext.parse::<u64>() {
                            Some(i)
                        } else {
                            None
                        }
                    } else {
                        None
                    }
                }};
            }

            return match idx!(file_name) {
                // if file has not been compressed index is extension
                Some(i) => Some(i),
                // try from file_stem, to handle file with compression ext
                None => idx!(file_name.file_stem().map(PathBuf::from)?),
            };
        }
        None
    }

    // list all files belonging to us. It returns a vec of tuples being
    // (index, metadata, path)
    #[inline(always)]
    fn list_files(&self) -> Result<Vec<(u64, Metadata, PathBuf)>, Error> {
        let mut out = vec![];

        for d in self.dir.read_dir()? {
            let de = d?;
            let p = de.path().canonicalize()?;
            // we skip self.file_path() as it must be last item
            if p == self.file_path() {
                continue;
            }
            if let Some(i) = self.file_index(&p) {
                out.push((i, p.metadata()?, p))
            }
        }

        // file currently modified must be the last one
        let last = self.file_path();
        if last.exists() {
            out.push((out.len() as u64, last.metadata()?, last));
        }

        Ok(out)
    }

    /// Exposes the list of files belonging to the rotating [File].
    #[inline]
    pub fn files_sorted_by_index(&self) -> Result<Vec<PathBuf>, Error> {
        let mut files = self.list_files()?;
        files.sort_by_key(|(i, _, _)| *i);
        Ok(files.into_iter().map(|(_, _, p)| p).collect())
    }

    /// Returns the size of the rotating [File]. The size is computed by
    /// summing up all the files (compressed or not) belonging to the file
    #[inline]
    pub fn size(&self) -> Result<u64, Error> {
        Ok(self
            .list_files()?
            .iter()
            .map(|(_, m, _)| file_size(m))
            .sum())
    }

    /// Manually rotate [File]. If compression is enabled, a thread
    /// will be started to compress the file being rotated. In the mean time
    /// you can continue using the [File].
    #[inline]
    pub fn rotate(&mut self) -> Result<(), Error> {
        if let Some(f) = self.writer.as_mut() {
            f.flush()?;

            // we wait compression routines to be done not to race files
            self.wait_compress()?;

            let mut files = self.list_files()?;
            files.sort_by_key(|(i, _, _)| *i);
            let i = files.last().map(|(i, _, _)| *i).unwrap_or(0);

            let archive_path = add_extension(self.file_path(), (i + 1).to_string());

            // we rename file to store archive
            fs::rename(self.file_path(), &archive_path)?;

            // we check if we don't exceed maximum size
            let size = self.size()?;

            if let Some(max_size) = self.max_size.map(|m| m.in_bytes()) {
                // we need to remove some files
                if size >= max_size {
                    // we get files ordered by mtime (oldest first)
                    let mut files = self.list_files()?;
                    // just used as default not to panic on m.modified
                    let def = SystemTime::now();
                    files.sort_by_key(|(i, m, _)| (*i, m.modified().unwrap_or(def)));
                    files.reverse();
                    let mut free = size - max_size;

                    while let Some((_, meta, path)) = files.pop() {
                        // we remove at least one file, in case
                        // size == max_size
                        fs::remove_file(path)?;
                        free = free.saturating_sub(file_size(&meta));
                        // no more space to make
                        if free == 0 {
                            break;
                        }
                    }
                }
            }

            if let Some(compression) = self.compression {
                // may have been deleted by maximum size check
                if archive_path.is_file() {
                    let mode = {
                        let f = || {
                            #[cfg(not(unix))]
                            return None;
                            #[cfg(unix)]
                            return self.ext.mode;
                        };
                        f()
                    };

                    self.compress_job = Some(std::thread::spawn(move || {
                        compression.compress(archive_path, mode)
                    }));
                }
            }

            return self.init_create_append();
        }
        Ok(())
    }

    #[inline(always)]
    fn should_rotate(&self) -> bool {
        if let Some(t) = self.trigger.as_ref() {
            return match t {
                Trigger::Size(s) => ByteSize::from_bytes(self.size) >= *s,
                Trigger::Time(d) => {
                    if let Some(open_instant) = self.created {
                        SystemTime::now().duration_since(open_instant).unwrap() >= *d
                    } else {
                        false
                    }
                }
            };
        }
        false
    }

    #[inline(always)]
    fn init_create_append(&mut self) -> Result<(), Error> {
        let opts = {
            let mut opts = fs::File::options();
            #[cfg(target_family = "unix")]
            {
                if let Some(mode) = self.ext.mode {
                    opts.mode(mode);
                }

                if let Some(flags) = self.ext.flags {
                    opts.custom_flags(flags);
                }
            }
            opts.append(true).create(true);
            opts
        };

        let fd = opts.open(self.file_path())?;

        let m = fd.metadata()?;
        self.size = file_size(&m);
        self.created = Some(
            // we attempt to get creation time
            m.created()
                // if we fail we take modification time
                .unwrap_or(
                    m.modified()
                        // if we fail again we take now
                        .unwrap_or(SystemTime::now()),
                ),
        );
        self.writer = Some(io::BufWriter::new(fd));
        Ok(())
    }

    #[inline]
    fn wait_compress(&mut self) -> Result<(), Error> {
        if self.compression.is_none() || self.compress_job.is_none() {
            return Ok(());
        }

        if let Some(h) = self.compress_job.take() {
            return h
                .join()
                .expect("cannot join compression thread")
                .map_err(Error::from);
        }

        Ok(())
    }

    /// Attempts to sync data to disk.
    ///
    /// # Warning
    /// This call will also wait for any ongoing
    /// compression routine to end. If a big file
    /// is currently under compression calling this method
    /// may block the program for some time.
    #[inline]
    pub fn sync(&mut self) -> Result<(), Error> {
        self.flush()?;
        self.wait_compress()
    }
}

impl Drop for File {
    fn drop(&mut self) {
        // this silently waits for compression jobs
        // to avoid any race panic or data corruptions
        // if you ever want to get a chance to handle compression
        // error call wait_compress before structure
        // is dropped.
        let _ = self.sync();
    }
}

#[cfg(test)]
mod test {
    use std::{
        io::{BufRead, BufReader, Write},
        time::{Duration, Instant},
    };

    use huby::ByteSize;

    use crate::OpenOptions;

    use super::Compression;
    use super::File;
    use super::Trigger;

    #[test]
    fn test() {
        let td = tempfile::tempdir().unwrap();
        let p = td.path().join("log");
        let mut f = File::create_append(&p).unwrap();
        // we rotate 199 times so we end up with 200 files (+1 for current)
        for _ in 0..199 {
            writeln!(f, "test").unwrap();
            f.rotate().unwrap();
        }

        writeln!(f, "test").unwrap();
        f.flush().unwrap();

        assert_eq!(f.files_sorted_by_index().unwrap().len(), 200);

        let r = BufReader::new(f.open_options().open(p).unwrap());
        let mut c = 0;
        for l in r.lines() {
            let l = l.unwrap();
            assert_eq!(l, "test");
            c += 1;
        }
        assert_eq!(c, 200)
    }

    #[test]
    fn test_time_rotate() {
        let td = tempfile::tempdir().unwrap();
        let p = td.path().join("log");
        let mut f = OpenOptions::new()
            .trigger(Duration::from_millis(500).into())
            .create_append(&p)
            .unwrap();

        let start = Instant::now();

        let mut c = 0usize;
        while Instant::now().checked_duration_since(start).unwrap() < Duration::from_secs(2) {
            writeln!(f, "test").unwrap();
            c = c.saturating_add(1);
        }

        f.sync().unwrap();

        assert_eq!(f.files_sorted_by_index().unwrap().len(), 5);

        let r = BufReader::new(f.open_options().open(p).unwrap());
        assert_eq!(r.lines().count(), c)
    }

    #[test]
    fn test_size_rotate() {
        let td = tempfile::tempdir().unwrap();

        let p = td.path().join("log");
        let mut f = OpenOptions::new()
            .trigger(ByteSize::from_bytes(50).into())
            .create_append(&p)
            .unwrap();

        // we rotate every 10 iteration
        for _ in 0..100 {
            // we write 5 bytes
            writeln!(f, "test").unwrap();
        }

        f.flush().unwrap();

        assert_eq!(f.files_sorted_by_index().unwrap().len(), 10);
        assert_eq!(f.size().unwrap(), 500);
        let r = BufReader::new(f.open_options().open(p).unwrap());

        assert_eq!(r.lines().count(), 100);
    }

    #[test]
    fn test_compression() {
        let td = tempfile::tempdir().unwrap();
        let p = td.path().join("log");
        let mut f = OpenOptions::new()
            .trigger(Trigger::Size(ByteSize::from_bytes(50)))
            .compression(Compression::Gzip)
            .create_append(&p)
            .unwrap();

        // we rotate every 10 iteration
        for _ in 0..100 {
            // we write 5 bytes
            writeln!(f, "test").unwrap();
        }

        f.flush().unwrap();
        f.wait_compress().unwrap();

        assert_eq!(f.files_sorted_by_index().unwrap().len(), 10);
        assert_eq!(f.size().unwrap(), 401);

        let lines = BufReader::new(f.open_options().open(p).unwrap()).lines();
        assert_eq!(lines.count(), 100)
    }

    #[test]
    fn test_max_size() {
        let td = tempfile::tempdir().unwrap();

        let p = td.path().join("log");
        let mut f = OpenOptions::new()
            .trigger(ByteSize::from_bytes(50).into())
            .max_size(ByteSize::from_bytes(200))
            .create_append(&p)
            .unwrap();

        for _ in 0..10000 {
            writeln!(f, "test").unwrap();
        }

        f.flush().unwrap();

        let files = f.files_sorted_by_index().unwrap();
        assert_eq!(files.len(), 4);
        assert_eq!(f.size().unwrap(), 200);
        for f in files {
            println!("{f:?}");
        }
        let lines = BufReader::new(f.open_options().open(p).unwrap()).lines();
        // even though we wrote 10_000 lines we should see
        // only 40, (200/50) * 10
        assert_eq!(lines.count(), 40)
    }

    #[test]
    fn test_max_size_with_compression() {
        let td = tempfile::tempdir().unwrap();

        let mut f = OpenOptions::new()
            .trigger(ByteSize::from_kb(1).into())
            .max_size(ByteSize::from_kb(2))
            .compression(Compression::Gzip)
            .create_append(td.path().join("log"))
            .unwrap();

        for _ in 0..20000 {
            writeln!(f, "test").unwrap();
        }

        f.flush().unwrap();
        f.wait_compress().unwrap();

        let files = f.files_sorted_by_index().unwrap();
        assert_eq!(files.len(), 26);
        assert!(f.size().unwrap() <= ByteSize::from_kb(2).in_bytes());
    }

    #[test]
    fn test_read_order() {
        let td = tempfile::tempdir().unwrap();
        let p = td.path().join("log");
        let mut opts = OpenOptions::new();
        opts.trigger(Trigger::Size(ByteSize::from_kb(1)))
            .compression(Compression::Gzip);
        let mut f = opts.create_append(&p).unwrap();

        for i in 0..20_000 {
            writeln!(f, "{i}").unwrap();
        }

        f.flush().unwrap();
        f.wait_compress().unwrap();

        assert_eq!(f.list_files().unwrap().len(), 107);

        let lines = BufReader::new(opts.open(p).unwrap())
            .lines()
            .map_while(Result::ok)
            .flat_map(|l| l.parse::<usize>())
            .collect::<Vec<usize>>();

        assert_eq!(lines.len(), 20_000);

        let mut prev = 0;
        for i in lines {
            if i == 0 {
                prev = i;
                continue;
            }
            assert!(i > prev);
            prev = i
        }
    }
}
