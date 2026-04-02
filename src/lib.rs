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
//!   the sum of all files sizes goes beyond the limit
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

use core::debug_assert;
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
    /// Size based trigger: will rotate file when current file
    /// reaches a given size.
    Size(ByteSize),
    /// Duration based trigger: will rotate file when duration since
    /// file creation reaches a given duration.
    Time(Duration),
    /// Combined trigger: will rotate file when either the size limit
    /// is reached or the time duration has elapsed, whichever comes first.
    SizeOrTime(ByteSize, Duration),
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

impl Trigger {
    /// Creates a `Trigger` from optional time and size parameters.
    ///
    /// Returns `None` if both parameters are `None`.
    /// Otherwise, returns the appropriate `Trigger` variant:
    /// - `Trigger::Size` if only size is provided
    /// - `Trigger::Time` if only time is provided
    /// - `Trigger::SizeOrTime` if both are provided
    ///
    /// # Examples
    ///
    /// ```
    /// use std::time::Duration;
    /// use huby::ByteSize;
    /// use firo::Trigger;
    ///
    /// // Size-only trigger
    /// let trigger = Trigger::from_options(None, Some(ByteSize::from_kb(1)));
    /// assert!(matches!(trigger, Some(Trigger::Size(_))));
    ///
    /// // Time-only trigger
    /// let trigger = Trigger::from_options(Some(Duration::from_secs(3600)), None);
    /// assert!(matches!(trigger, Some(Trigger::Time(_))));
    ///
    /// // Combined trigger
    /// let trigger = Trigger::from_options(Some(Duration::from_secs(300)), Some(ByteSize::from_mb(10)));
    /// assert!(matches!(trigger, Some(Trigger::SizeOrTime(_, _))));
    ///
    /// // No trigger
    /// let trigger = Trigger::from_options(None, None);
    /// assert!(matches!(trigger, None));
    /// ```
    pub fn from_options(t: Option<Duration>, s: Option<ByteSize>) -> Option<Self> {
        match (t, s) {
            (None, None) => None,
            (None, Some(s)) => Some(Self::Size(s)),
            (Some(t), None) => Some(Self::Time(t)),
            (Some(t), Some(s)) => Some(Self::SizeOrTime(s, t)),
        }
    }
}

/// Enumeration to configure compression type for rotated log files.
#[derive(Debug, Clone, Copy)]
pub enum Compression {
    /// Gzip compression using the flate2 crate.
    Gzip,
}

/// Errors that can occur during file compression operations.
#[derive(Debug, Error)]
pub enum CompressionError {
    /// Error occurred while persisting temporary file used for compression to disk.
    #[error("persist: {0}")]
    Persist(#[from] PersistError),
    /// I/O error during compression operations.
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
        // we create temporary file in the current path directory
        // to avoid cross file system persistence error
        let tmp = NamedTempFile::new_in(path.parent().ok_or(io::Error::new(
            io::ErrorKind::NotFound,
            "cannot create temporary file",
        ))?)?;
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
    /// Creates a new `OpenOptions` with default values.
    ///
    /// This is equivalent to `OpenOptions::default()`.
    ///
    /// # Examples
    ///
    /// ```
    /// use firo::OpenOptions;
    ///
    /// let options = OpenOptions::new();
    /// ```
    pub fn new() -> Self {
        Self::default()
    }

    /// Sets the maximum total size allowed for all rotating [File] instances.
    ///
    /// When the combined size of all rotated files exceeds this threshold,
    /// the oldest files are automatically deleted to stay within the limit.
    /// This does not affect the current active file being written to.
    ///
    /// # Examples
    ///
    /// ```
    /// use firo::OpenOptions;
    ///
    /// // Limit total rotated files to 10MB
    /// let options = OpenOptions::new()
    ///     .max_size(huby::ByteSize::from_mb(10));
    /// ```
    pub fn max_size(&mut self, m: ByteSize) -> &mut Self {
        self.max_size = Some(m);
        self
    }

    /// Sets the [Trigger] used to rotate the file.
    ///
    /// This method replaces any existing trigger with the provided one.
    /// Use [opt_trigger](OpenOptions::opt_trigger) to optionally set or clear a trigger.
    ///
    /// # Examples
    ///
    /// ```
    /// use firo::{OpenOptions, Trigger};
    /// use std::time::Duration;
    ///
    /// // Set a time-based trigger
    /// let options = OpenOptions::new()
    ///     .trigger(Trigger::Time(Duration::from_secs(3600)));
    ///
    /// // Set a size-based trigger
    /// let options = OpenOptions::new()
    ///     .trigger(Trigger::Size(huby::ByteSize::from_mb(1)));
    /// ```
    pub fn trigger(&mut self, t: Trigger) -> &mut Self {
        self.trigger = Some(t);
        self
    }

    /// Sets or clears the [Trigger] used to rotate the file.
    ///
    /// Unlike [trigger](OpenOptions::trigger), this method accepts an `Option<Trigger>`,
    /// allowing you to either set a new trigger or clear any existing trigger by passing `None`.
    ///
    /// # Examples
    ///
    /// ```
    /// use firo::{OpenOptions, Trigger};
    /// use std::time::Duration;
    ///
    /// // Set a trigger
    /// let options = OpenOptions::new()
    ///     .opt_trigger(Some(Trigger::Time(Duration::from_secs(3600))));
    /// ```
    pub fn opt_trigger(&mut self, t: Option<Trigger>) -> &mut Self {
        self.trigger = t;
        self
    }

    /// Enables compression for rotated files.
    ///
    /// When compression is enabled, rotated files will be compressed using the specified
    /// compression algorithm. The current active file being written to is never compressed.
    ///
    /// # Examples
    ///
    /// ```
    /// use firo::{OpenOptions, Compression};
    ///
    /// // Enable gzip compression for rotated files
    /// let options = OpenOptions::new()
    ///     .compression(Compression::Gzip);
    /// ```
    pub fn compression(&mut self, c: Compression) -> &mut Self {
        self.compression = Some(c);
        self
    }

    /// Creates a new [File] in append mode using the configured options.
    ///
    /// The file will be created if it doesn't exist, or appended to if it does.
    /// Rotation triggers and other options will be applied to this file.
    ///
    /// # Errors
    ///
    /// Returns an error if the file cannot be created or opened for writing.
    ///
    /// # Examples
    ///
    /// ```
    /// use firo::OpenOptions;
    ///
    /// let mut file = OpenOptions::new()
    ///     .create_append("/tmp/my_log.log")
    ///     .expect("Failed to create log file");
    /// ```
    pub fn create_append<P: AsRef<Path>>(self, path: P) -> Result<File, Error> {
        File::create_append_with_options(path, self)
    }

    /// Opens an existing [File] for reading using the configured options.
    ///
    /// This is primarily used to read from rotated log files.
    ///
    /// # Errors
    ///
    /// Returns an error if the file cannot be opened for reading.
    ///
    /// # Examples
    ///
    /// ```
    /// use firo::OpenOptions;
    ///
    /// let file = OpenOptions::new()
    ///     .open("/tmp/my_log.log")
    ///     .expect("Failed to open log file");
    /// ```
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

/// A rotating file handle that supports automatic rotation based on size or time triggers.
///
/// Files are rotated when any of the configured triggers are met. Rotated files are
/// renamed with an incrementing index suffix (e.g., `file.1`, `file.2`).
///
/// # Important Notes
///
/// - When compression is enabled, a new thread is spawned at rotation time to
///   compress the rotated file asynchronously. This allows write operations to
///   continue without blocking.
/// - The compression thread will be joined when the [File] is dropped or explicitly
///   closed, ensuring all compression operations complete.
///
/// # Examples
///
/// ```
/// use firo::{File, OpenOptions, Trigger};
/// use std::time::Duration;
/// use huby::ByteSize;
/// use std::io::Write;
///
/// // use temporary directory for test purposes
/// let td = tempfile::tempdir().unwrap();
/// let p = td.path().join("my_log.log");
/// // Create a file that rotates every 1MB or every hour
/// let mut file = OpenOptions::new()
///     .trigger(Trigger::SizeOrTime(
///         ByteSize::from_mb(1),
///         Duration::from_secs(3600)
///     ))
///     .create_append(&p)
///     .unwrap();
///
/// // Write data - file will auto-rotate when triggers are met
/// writeln!(file, "Log entry").unwrap();
/// ```
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
    ///
    /// This can be useful for creating new files with the same configuration
    /// or for inspecting the current file's configuration.
    ///
    /// # Examples
    ///
    /// ```
    /// use firo::File;
    ///
    /// let file = File::create_append("/tmp/log.txt").unwrap();
    /// let options = file.open_options();
    /// ```
    pub fn open_options(&self) -> OpenOptions {
        OpenOptions {
            max_size: self.max_size,
            trigger: self.trigger,
            compression: self.compression,
            #[cfg(target_family = "unix")]
            ext: self.ext,
        }
    }

    /// Creates a new rotating [File] with default options.
    ///
    /// This is equivalent to `File::create_append_with_options(file, OpenOptions::default())`.
    /// The file will be created if it doesn't exist, or appended to if it does.
    ///
    /// # Errors
    ///
    /// Returns an error if the file cannot be created or opened for writing.
    ///
    /// # Examples
    ///
    /// ```
    /// use firo::File;
    ///
    /// let mut file = File::create_append("/tmp/my_log.log")
    ///     .expect("Failed to create log file");
    /// ```
    pub fn create_append<P: AsRef<Path>>(file: P) -> Result<Self, Error> {
        Self::create_append_with_options(file, OpenOptions::default())
    }

    /// Opens an existing rotating [File] with specified [OpenOptions].
    ///
    /// This method is primarily used for reading from existing rotated log files
    /// while maintaining consistent configuration.
    ///
    /// # Errors
    ///
    /// Returns an error if the file cannot be opened for reading or if the
    /// provided options are incompatible with the existing file.
    ///
    /// # Examples
    ///
    /// ```
    /// use firo::{File, OpenOptions};
    ///
    /// let options = OpenOptions::new();
    /// let file = File::open_with_options("/tmp/my_log.log", options)
    ///     .expect("Failed to open log file");
    /// ```
    pub fn open_with_options<P: AsRef<Path>>(file: P, opts: OpenOptions) -> Result<Self, Error> {
        let mut f = Self::new(file, opts)?;

        f.reader = Some(Reader::from_file(&f)?);

        Ok(f)
    }

    /// Creates a new rotating [File] with custom [OpenOptions].
    ///
    /// This is the most flexible way to create a rotating file, allowing
    /// full configuration of triggers, compression, and size limits.
    ///
    /// # Errors
    ///
    /// Returns an error if the file cannot be created or if the provided
    /// options are invalid.
    ///
    /// # Examples
    ///
    /// ```
    /// use firo::{File, OpenOptions, Trigger};
    /// use std::time::Duration;
    ///
    /// let mut options = OpenOptions::new();
    /// options.trigger(Trigger::Time(Duration::from_secs(3600)))
    ///        .compression(firo::Compression::Gzip);
    ///
    /// let mut file = File::create_append_with_options("/tmp/my_log.txt", options)
    ///     .expect("Failed to create log file");
    /// ```
    pub fn create_append_with_options<P: AsRef<Path>>(
        file: P,
        opts: OpenOptions,
    ) -> Result<Self, Error> {
        let mut f = Self::new(file, opts)?;

        f.init_create_append()?;

        Ok(f)
    }

    /// Returns the path to the current active [File] being written.
    ///
    /// This path always points to the current file where new writes will go,
    /// not to any rotated files.
    ///
    /// # Examples
    ///
    /// ```
    /// use firo::File;
    /// use std::path::PathBuf;
    ///
    /// let file = File::create_append("/tmp/my_log.log").unwrap();
    /// let path = file.file_path();
    /// assert_eq!(file.file_path(), PathBuf::from("/tmp/my_log.log"));
    /// ```
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

    /// Returns a list of all rotated files sorted by their rotation index.
    ///
    /// This method returns paths to all rotated files associated with this [File],
    /// sorted from oldest (lowest index) to newest (highest index). The current
    /// active file being written to will be the last vector item.
    ///
    /// Rotated files follow the naming pattern: `prefix.1`, `prefix.2`, etc., where
    /// the number represents the rotation index.
    ///
    /// # Returns
    ///
    /// A vector of [PathBuf] objects representing the rotated files, sorted by index.
    ///
    /// # Errors
    ///
    /// Returns an error on any failure during the listing process.
    #[inline]
    pub fn files_sorted_by_index(&self) -> Result<Vec<PathBuf>, Error> {
        let mut files = self.list_files()?;
        files.sort_by_key(|(i, _, _)| *i);
        Ok(files.into_iter().map(|(_, _, p)| p).collect())
    }

    /// Returns the total size in bytes of all files in the rotating file set.
    ///
    /// This method calculates the combined size of:
    /// - The current active file being written to
    /// - All rotated files (both compressed or uncompressed)
    ///
    /// The returned size represents the actual disk usage of all files
    /// associated with this rotating file instance.
    ///
    /// # Returns
    ///
    /// The total size in bytes as a `u64`. For compressed files, this uses
    /// the compressed size on disk, not the original uncompressed size.
    ///
    /// # Errors
    ///
    /// Returns an error if any of the files cannot be accessed or if their
    /// metadata cannot be read.
    #[inline]
    pub fn size(&self) -> Result<u64, Error> {
        Ok(self
            .list_files()?
            .iter()
            .map(|(_, m, _)| file_size(m))
            .sum())
    }

    /// Manually triggers rotation of the current file.
    ///
    /// This method performs the following operations:
    /// 1. Flushes any buffered writes to disk
    /// 2. Waits for any ongoing compression to complete
    /// 3. Renames the current file with the next available rotation index
    /// 4. Creates a new current file for continued writing
    /// 5. If compression is enabled, spawns a new thread to compress the rotated file
    /// 6. If max_size is configured, deletes oldest files to stay within the limit
    ///
    /// # Performance Characteristics
    ///
    /// - The method may block briefly while waiting for compression to complete
    /// - File I/O operations are performed synchronously
    /// - Compression happens asynchronously in a separate thread
    /// - Write operations can continue immediately after this method returns
    ///
    /// # Errors
    ///
    /// Returns an error if critical operation fails during rotation:
    /// - Flushing the current file fails
    /// - Compression thread fails
    /// - File renaming operations fail
    /// - Creating the new current file fails
    /// - File deletion (for size management) fails
    ///
    /// # See Also
    ///
    /// - [sync](File::sync): Synchronize writes and wait for compression
    /// - [files_sorted_by_index](File::files_sorted_by_index): List rotated files
    /// - [size](File::size): Check total disk usage
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
                        let r = compression.compress(archive_path, mode);
                        debug_assert!(r.is_ok(), "compress job failed: {:?}", r);
                        r
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
                Trigger::Time(d) => self
                    .created
                    .map(|c| SystemTime::now().duration_since(c).unwrap() >= *d)
                    .unwrap_or_default(),
                Trigger::SizeOrTime(s, d) => {
                    ByteSize::from_bytes(self.size) >= *s
                        || self
                            .created
                            .map(|c| SystemTime::now().duration_since(c).unwrap() >= *d)
                            .unwrap_or_default()
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

    /// Synchronizes all buffered data to disk and waits for compression to complete.
    ///
    /// This method performs two operations:
    /// 1. Flushes all buffered writes to the underlying file
    /// 2. Waits for any ongoing compression operations to finish
    ///
    /// # Performance Considerations
    ///
    /// If compression is enabled and a large file is currently being compressed,
    /// this call may block for a significant amount of time while waiting for
    /// the compression to complete. Consider using [flush](File::flush) if you
    /// only need to ensure writes are durably stored without waiting for compression.
    ///
    /// # Errors
    ///
    /// Returns an error if flushing the file fails or if compression routine failed.
    ///
    /// # Examples
    ///
    /// ```
    /// use firo::File;
    /// use std::io::Write;
    ///
    /// let mut file = File::create_append("/tmp/log.txt").unwrap();
    /// writeln!(file, "Important data").unwrap();
    ///
    /// // Ensure everything is safely written and compressed
    /// file.sync().expect("Failed to sync");
    /// ```
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

        // not stable number of files (4 or 5) but important is more
        // that we can later read the good numbers of lines written
        assert!(f.files_sorted_by_index().unwrap().len() >= 4);

        let r = BufReader::new(f.open_options().open(p).unwrap());
        assert_eq!(r.lines().count(), c)
    }

    #[test]
    fn test_size_or_time_rotate_time() {
        // We test SizeOrTime trigger but only triggering on time
        let td = tempfile::tempdir().unwrap();
        let p = td.path().join("log");
        let mut f = OpenOptions::new()
            .trigger(Trigger::SizeOrTime(
                ByteSize::from_mb(50),
                Duration::from_millis(500),
            ))
            .create_append(&p)
            .unwrap();

        let start = Instant::now();

        let mut c = 0usize;
        while Instant::now().checked_duration_since(start).unwrap() < Duration::from_secs(2) {
            writeln!(f, "test").unwrap();
            c = c.saturating_add(1);
        }

        f.sync().unwrap();

        // not stable number of files (4 or 5) but important is more
        // that we can later read the good numbers of lines written
        assert!(f.files_sorted_by_index().unwrap().len() >= 4);

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
    fn test_size_or_time_rotate_size() {
        // We test SizeOrTime trigger but only triggering on size
        let td = tempfile::tempdir().unwrap();

        let p = td.path().join("log");
        let mut f = OpenOptions::new()
            .trigger(Trigger::SizeOrTime(
                ByteSize::from_bytes(50),
                Duration::from_secs(600),
            ))
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
